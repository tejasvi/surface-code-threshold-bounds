import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11484 = true := by
  decide +kernel

theorem tot11484 : totK PD2M8K2 D2M8K2.t11484 = [0, 0, 244046457287, 498806660073, 148455751378, 11551010310, 0, 0] := by
  decide +kernel

theorem rows11485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11485 = true := by
  decide +kernel

theorem tot11485 : totK PD2M8K2 D2M8K2.t11485 = [0, 0, 161185736924, 447984384877, 281865028524, 19967460746, 0, 0] := by
  decide +kernel

theorem rows11486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11486 = true := by
  decide +kernel

theorem tot11486 : totK PD2M8K2 D2M8K2.t11486 = [0, 0, 171872442219, 461013584851, 242241435959, 10059424770, 0, 0] := by
  decide +kernel

theorem rows11487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11487 = true := by
  decide +kernel

theorem tot11487 : totK PD2M8K2 D2M8K2.t11487 = [0, 0, 194898241300, 451092541903, 234186256029, 22475569713, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
