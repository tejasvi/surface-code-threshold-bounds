import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3580 = true := by
  decide +kernel

theorem tot3580 : totK PD2M8K2 D2M8K2.t3580 = [0, 182851891860, 465452629775, 225953924596, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows3581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3581 = true := by
  decide +kernel

theorem tot3581 : totK PD2M8K2 D2M8K2.t3581 = [0, 33508730992, 311785753776, 456126029300, 87029183770, 1164319620, 0, 0] := by
  decide +kernel

theorem rows3582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3582 = true := by
  decide +kernel

theorem tot3582 : totK PD2M8K2 D2M8K2.t3582 = [0, 0, 206149427865, 467786411198, 174690899379, 11819130176, 0, 0] := by
  decide +kernel

theorem rows3583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3583 = true := by
  decide +kernel

theorem tot3583 : totK PD2M8K2 D2M8K2.t3583 = [0, 201689224253, 459745837251, 232322563745, 17664910200, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
