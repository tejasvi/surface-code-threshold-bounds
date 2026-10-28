import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4704 = true := by
  decide +kernel

theorem tot4704 : totK PD2M8K2 D2M8K2.t4704 = [0, 0, 0, 287644589395, 501429074805, 119144960644, 4009909289, 0] := by
  decide +kernel

theorem rows4705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4705 = true := by
  decide +kernel

theorem tot4705 : totK PD2M8K2 D2M8K2.t4705 = [0, 0, 105119095157, 352274813592, 365797853276, 72005616821, 1149959346, 0] := by
  decide +kernel

theorem rows4706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4706 = true := by
  decide +kernel

theorem tot4706 : totK PD2M8K2 D2M8K2.t4706 = [0, 0, 162878032843, 444195833244, 280449637315, 30435264497, 0, 0] := by
  decide +kernel

theorem rows4707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4707 = true := by
  decide +kernel

theorem tot4707 : totK PD2M8K2 D2M8K2.t4707 = [0, 0, 157260371766, 457785294954, 267917213772, 16767125389, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
