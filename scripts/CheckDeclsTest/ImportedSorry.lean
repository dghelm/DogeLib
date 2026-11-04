module

public import CheckDeclsForeignSorry

/-! Fixtures that inherit an unfinished proof from outside the checked scope. -/

public section

namespace CheckDeclsTest.ImportedSorry

/-- A theorem that inherits `sorryAx` through an imported theorem. -/
theorem inherited : 2 = 3 := CheckDeclsForeignSorry.unfinished

/-- A further use of the imported unfinished proof. -/
theorem downstream : 2 = 3 := inherited

end CheckDeclsTest.ImportedSorry
