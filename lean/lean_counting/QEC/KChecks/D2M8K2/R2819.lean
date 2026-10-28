import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11276 = true := by
  decide +kernel

theorem tot11276 : totK PD2M8K2 D2M8K2.t11276 = [0, 18846686532, 300815731221, 461436998856, 85127456844, 1206465782, 0, 0] := by
  decide +kernel

theorem rows11277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11277 = true := by
  decide +kernel

theorem tot11277 : totK PD2M8K2 D2M8K2.t11277 = [0, 130479377927, 407247339310, 341137751959, 39744699327, 0, 0, 0] := by
  decide +kernel

theorem rows11278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11278 = true := by
  decide +kernel

theorem tot11278 : totK PD2M8K2 D2M8K2.t11278 = [0, 210721192746, 481217798645, 207801044770, 11405872210, 0, 0, 0] := by
  decide +kernel

theorem rows11279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11279 = true := by
  decide +kernel

theorem tot11279 : totK PD2M8K2 D2M8K2.t11279 = [0, 167943004862, 463049119824, 238389687808, 15470236839, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
