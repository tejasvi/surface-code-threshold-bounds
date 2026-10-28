import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1036 = true := by
  decide +kernel

theorem tot1036 : totK PD2M8K2 D2M8K2.t1036 = [165952213950, 439136212039, 271346222962, 29615452831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1037 = true := by
  decide +kernel

theorem tot1037 : totK PD2M8K2 D2M8K2.t1037 = [155082416523, 453989246612, 269943154210, 19620913118, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1038 = true := by
  decide +kernel

theorem tot1038 : totK PD2M8K2 D2M8K2.t1038 = [0, 209628074588, 490691576048, 168455657234, 8143100748, 0, 0, 0] := by
  decide +kernel

theorem rows1039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1039 = true := by
  decide +kernel

theorem tot1039 : totK PD2M8K2 D2M8K2.t1039 = [84672624166, 302441507428, 375763698178, 111266422372, 4906626486, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
