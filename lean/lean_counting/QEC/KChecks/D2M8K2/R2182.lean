import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8728 = true := by
  decide +kernel

theorem tot8728 : totK PD2M8K2 D2M8K2.t8728 = [0, 0, 155065940111, 453759655881, 259975713217, 16366555810, 0, 0] := by
  decide +kernel

theorem rows8729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8729 = true := by
  decide +kernel

theorem tot8729 : totK PD2M8K2 D2M8K2.t8729 = [0, 0, 0, 272034815731, 475990142492, 122593263586, 4140770520, 0] := by
  decide +kernel

theorem rows8730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8730 = true := by
  decide +kernel

theorem tot8730 : totK PD2M8K2 D2M8K2.t8730 = [0, 0, 139243734910, 370992444061, 294465062503, 60825034295, 1179991115, 0] := by
  decide +kernel

theorem rows8731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8731 = true := by
  decide +kernel

theorem tot8731 : totK PD2M8K2 D2M8K2.t8731 = [0, 0, 169832521741, 464260554807, 249893861361, 18252358503, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
