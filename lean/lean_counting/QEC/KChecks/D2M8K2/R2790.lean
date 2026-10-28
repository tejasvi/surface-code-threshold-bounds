import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11160 = true := by
  decide +kernel

theorem tot11160 : totK PD2M8K2 D2M8K2.t11160 = [0, 175925739104, 460537429732, 235191533103, 16991714847, 0, 0, 0] := by
  decide +kernel

theorem rows11161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11161 = true := by
  decide +kernel

theorem tot11161 : totK PD2M8K2 D2M8K2.t11161 = [0, 150686192522, 440645402859, 269278684469, 18876887433, 0, 0, 0] := by
  decide +kernel

theorem rows11162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11162 = true := by
  decide +kernel

theorem tot11162 : totK PD2M8K2 D2M8K2.t11162 = [0, 0, 271867136321, 499175350158, 111755394035, 1369150432, 0, 0] := by
  decide +kernel

theorem rows11163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11163 = true := by
  decide +kernel

theorem tot11163 : totK PD2M8K2 D2M8K2.t11163 = [0, 134457132423, 391340724039, 354756216872, 46701410000, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
