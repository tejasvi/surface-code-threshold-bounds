import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4144 = true := by
  decide +kernel

theorem tot4144 : totK PD2M8K2 D2M8K2.t4144 = [0, 180183318095, 483543527382, 234389634778, 12169895203, 0, 0, 0] := by
  decide +kernel

theorem rows4145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4145 = true := by
  decide +kernel

theorem tot4145 : totK PD2M8K2 D2M8K2.t4145 = [0, 0, 286919354065, 516460181505, 97246423541, 1096505104, 0, 0] := by
  decide +kernel

theorem rows4146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4146 = true := by
  decide +kernel

theorem tot4146 : totK PD2M8K2 D2M8K2.t4146 = [0, 0, 220672141740, 498954063053, 164361612139, 5253830308, 0, 0] := by
  decide +kernel

theorem rows4147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4147 = true := by
  decide +kernel

theorem tot4147 : totK PD2M8K2 D2M8K2.t4147 = [0, 0, 191149612296, 448414964795, 212427885534, 16891742343, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
