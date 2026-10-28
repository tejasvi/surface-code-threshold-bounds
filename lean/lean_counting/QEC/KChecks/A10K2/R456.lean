import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1824 = true := by
  decide +kernel

theorem tot1824 : totK PA10K2 A10K2.t1824 = [0, 451221517985, 1768896528186, 1945234551891, 548528616877, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1825 = true := by
  decide +kernel

theorem tot1825 : totK PA10K2 A10K2.t1825 = [0, 250632753840, 1347531250046, 2193785790026, 1127153584771, 114310606417, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1826 = true := by
  decide +kernel

theorem tot1826 : totK PA10K2 A10K2.t1826 = [0, 0, 537437065111, 1869261844174, 1790338137111, 464108156158, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows1827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1827 = true := by
  decide +kernel

theorem tot1827 : totK PA10K2 A10K2.t1827 = [0, 573073781472, 1840291295579, 1785150005382, 553173425359, 57924830081, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
