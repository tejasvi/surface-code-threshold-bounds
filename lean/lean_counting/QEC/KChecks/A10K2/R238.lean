import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t952 = true := by
  decide +kernel

theorem tot952 : totK PA10K2 A10K2.t952 = [0, 0, 501233137592, 1932718867437, 2101949417563, 533720597062, 26806030479, 0, 0, 0] := by
  decide +kernel

theorem rows953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t953 = true := by
  decide +kernel

theorem tot953 : totK PA10K2 A10K2.t953 = [0, 412429632915, 1402163254966, 1598592906840, 1031666992063, 471176313930, 50491866487, 0, 0, 0] := by
  decide +kernel

theorem rows954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t954 = true := by
  decide +kernel

theorem tot954 : totK PA10K2 A10K2.t954 = [0, 371871431194, 1650507653403, 2082548144433, 795994087239, 62506613362, 0, 0, 0, 0] := by
  decide +kernel

theorem rows955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t955 = true := by
  decide +kernel

theorem tot955 : totK PA10K2 A10K2.t955 = [0, 0, 509664305837, 1855522450476, 1821192107184, 475583448052, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
