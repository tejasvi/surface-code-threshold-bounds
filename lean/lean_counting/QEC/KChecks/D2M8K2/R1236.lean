import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4944 = true := by
  decide +kernel

theorem tot4944 : totK PD2M8K2 D2M8K2.t4944 = [0, 177179649323, 464080806451, 244723752586, 14131463171, 0, 0, 0] := by
  decide +kernel

theorem rows4945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4945 = true := by
  decide +kernel

theorem tot4945 : totK PD2M8K2 D2M8K2.t4945 = [0, 68433758957, 334800996765, 407232257441, 84977050363, 1198073392, 0, 0] := by
  decide +kernel

theorem rows4946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4946 = true := by
  decide +kernel

theorem tot4946 : totK PD2M8K2 D2M8K2.t4946 = [0, 0, 199757954572, 477645563684, 183322971557, 12052611869, 0, 0] := by
  decide +kernel

theorem rows4947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4947 = true := by
  decide +kernel

theorem tot4947 : totK PD2M8K2 D2M8K2.t4947 = [0, 159457644122, 444578489241, 285304197432, 26898426202, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
