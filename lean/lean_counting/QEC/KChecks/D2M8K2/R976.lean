import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3904 = true := by
  decide +kernel

theorem tot3904 : totK PD2M8K2 D2M8K2.t3904 = [0, 0, 215022334981, 482621704757, 184547138231, 7947699043, 0, 0] := by
  decide +kernel

theorem rows3905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3905 = true := by
  decide +kernel

theorem tot3905 : totK PD2M8K2 D2M8K2.t3905 = [0, 90182705397, 332573212632, 398125946022, 97477510269, 1231290674, 0, 0] := by
  decide +kernel

theorem rows3906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3906 = true := by
  decide +kernel

theorem tot3906 : totK PD2M8K2 D2M8K2.t3906 = [0, 167215624231, 461776757431, 261372827605, 20857195417, 0, 0, 0] := by
  decide +kernel

theorem rows3907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3907 = true := by
  decide +kernel

theorem tot3907 : totK PD2M8K2 D2M8K2.t3907 = [0, 87994698789, 409995320561, 379616215111, 46404872681, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
