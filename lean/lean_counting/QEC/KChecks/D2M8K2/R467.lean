import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1868 = true := by
  decide +kernel

theorem tot1868 : totK PD2M8K2 D2M8K2.t1868 = [0, 0, 198204878516, 479463104649, 208829593493, 11056080877, 0, 0] := by
  decide +kernel

theorem rows1869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1869 = true := by
  decide +kernel

theorem tot1869 : totK PD2M8K2 D2M8K2.t1869 = [0, 0, 163887562577, 461069495814, 230289864519, 13144444366, 0, 0] := by
  decide +kernel

theorem rows1870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1870 = true := by
  decide +kernel

theorem tot1870 : totK PD2M8K2 D2M8K2.t1870 = [0, 0, 0, 302857307609, 464228257991, 76533227365, 1021600638, 0] := by
  decide +kernel

theorem rows1871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1871 = true := by
  decide +kernel

theorem tot1871 : totK PD2M8K2 D2M8K2.t1871 = [0, 0, 104239363842, 351912873885, 309788420488, 76305736775, 3552795014, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
