import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15512 = true := by
  decide +kernel

theorem tot15512 : totK PD2M8K2 D2M8K2.t15512 = [0, 162691190537, 481562609226, 243933668628, 10335814830, 0, 0, 0] := by
  decide +kernel

theorem rows15513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15513 = true := by
  decide +kernel

theorem tot15513 : totK PD2M8K2 D2M8K2.t15513 = [0, 0, 221394375991, 491371383396, 161865145002, 5455647540, 0, 0] := by
  decide +kernel

theorem rows15514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15514 = true := by
  decide +kernel

theorem tot15514 : totK PD2M8K2 D2M8K2.t15514 = [0, 140096049002, 431634960991, 302228431088, 36133049496, 0, 0, 0] := by
  decide +kernel

theorem rows15515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15515 = true := by
  decide +kernel

theorem tot15515 : totK PD2M8K2 D2M8K2.t15515 = [0, 153810003305, 422854623831, 280485703415, 27305464625, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
