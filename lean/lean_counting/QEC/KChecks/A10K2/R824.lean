import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3296 = true := by
  decide +kernel

theorem tot3296 : totK PA10K2 A10K2.t3296 = [0, 0, 547155537134, 1657799837628, 1700295898549, 738540953194, 153150958960, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3297 = true := by
  decide +kernel

theorem tot3297 : totK PA10K2 A10K2.t3297 = [0, 0, 297002103535, 1571815499619, 2137232543556, 834365184402, 63281320772, 0, 0, 0] := by
  decide +kernel

theorem rows3298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3298 = true := by
  decide +kernel

theorem tot3298 : totK PA10K2 A10K2.t3298 = [0, 0, 0, 470388421865, 1838438085251, 1868334164729, 485240062535, 31452573850, 0, 0] := by
  decide +kernel

theorem rows3299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3299 = true := by
  decide +kernel

theorem tot3299 : totK PA10K2 A10K2.t3299 = [0, 0, 466842231207, 1697434568445, 1855908087097, 679987632206, 60436323686, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
