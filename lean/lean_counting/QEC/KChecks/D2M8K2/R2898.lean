import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11592 = true := by
  decide +kernel

theorem tot11592 : totK PD2M8K2 D2M8K2.t11592 = [87489192441, 327023280436, 359628298228, 127472599941, 15864095392, 0, 0, 0] := by
  decide +kernel

theorem rows11593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11593 = true := by
  decide +kernel

theorem tot11593 : totK PD2M8K2 D2M8K2.t11593 = [0, 172506903808, 468027697219, 246766600697, 13530797253, 0, 0, 0] := by
  decide +kernel

theorem rows11594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11594 = true := by
  decide +kernel

theorem tot11594 : totK PD2M8K2 D2M8K2.t11594 = [36305858295, 213358211474, 442084748876, 197131459362, 8214505460, 0, 0, 0] := by
  decide +kernel

theorem rows11595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11595 = true := by
  decide +kernel

theorem tot11595 : totK PD2M8K2 D2M8K2.t11595 = [191606076159, 463654043581, 250336931493, 23388038350, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
