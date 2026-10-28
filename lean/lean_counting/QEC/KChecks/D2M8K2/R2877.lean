import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11508 = true := by
  decide +kernel

theorem tot11508 : totK PD2M8K2 D2M8K2.t11508 = [0, 166594156294, 435910638281, 249826378149, 48564283489, 2481160468, 0, 0] := by
  decide +kernel

theorem rows11509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11509 = true := by
  decide +kernel

theorem tot11509 : totK PD2M8K2 D2M8K2.t11509 = [0, 179712317002, 441554147036, 263852789908, 21132809524, 0, 0, 0] := by
  decide +kernel

theorem rows11510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11510 = true := by
  decide +kernel

theorem tot11510 : totK PD2M8K2 D2M8K2.t11510 = [0, 67740584699, 345600017376, 383188544550, 82457618520, 1198073392, 0, 0] := by
  decide +kernel

theorem rows11511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11511 = true := by
  decide +kernel

theorem tot11511 : totK PD2M8K2 D2M8K2.t11511 = [0, 0, 238417625537, 479866704325, 158079221816, 9482920370, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
