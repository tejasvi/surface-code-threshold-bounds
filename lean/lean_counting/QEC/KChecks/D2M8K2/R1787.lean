import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7148 = true := by
  decide +kernel

theorem tot7148 : totK PD2M8K2 D2M8K2.t7148 = [0, 170964537079, 480793982048, 236786512548, 13176035012, 0, 0, 0] := by
  decide +kernel

theorem rows7149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7149 = true := by
  decide +kernel

theorem tot7149 : totK PD2M8K2 D2M8K2.t7149 = [0, 0, 201130258277, 469978420782, 225439558173, 13908735795, 0, 0] := by
  decide +kernel

theorem rows7150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7150 = true := by
  decide +kernel

theorem tot7150 : totK PD2M8K2 D2M8K2.t7150 = [0, 85167078157, 261393151284, 404835480521, 143991245326, 2554132940, 0, 0] := by
  decide +kernel

theorem rows7151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7151 = true := by
  decide +kernel

theorem tot7151 : totK PD2M8K2 D2M8K2.t7151 = [0, 171870687712, 468251364980, 249894233009, 20179010831, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
