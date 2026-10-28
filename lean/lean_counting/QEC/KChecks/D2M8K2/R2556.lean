import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10224 = true := by
  decide +kernel

theorem tot10224 : totK PD2M8K2 D2M8K2.t10224 = [0, 173217593522, 463466160841, 267381513870, 17461553797, 0, 0, 0] := by
  decide +kernel

theorem rows10225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10225 = true := by
  decide +kernel

theorem tot10225 : totK PD2M8K2 D2M8K2.t10225 = [0, 176576894766, 469554096341, 244620258353, 16100820273, 0, 0, 0] := by
  decide +kernel

theorem rows10226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10226 = true := by
  decide +kernel

theorem tot10226 : totK PD2M8K2 D2M8K2.t10226 = [0, 0, 197042067009, 459492559017, 237481600921, 24261412795, 0, 0] := by
  decide +kernel

theorem rows10227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10227 = true := by
  decide +kernel

theorem tot10227 : totK PD2M8K2 D2M8K2.t10227 = [0, 0, 193941755526, 487764234646, 210035447645, 6543040663, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
