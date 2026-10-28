import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5784 = true := by
  decide +kernel

theorem tot5784 : totK PD2M8K2 D2M8K2.t5784 = [153605049212, 454284756602, 278102708922, 21974823335, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5785 = true := by
  decide +kernel

theorem tot5785 : totK PD2M8K2 D2M8K2.t5785 = [0, 215102816080, 491658304072, 179052271292, 9561477370, 0, 0, 0] := by
  decide +kernel

theorem rows5786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5786 = true := by
  decide +kernel

theorem tot5786 : totK PD2M8K2 D2M8K2.t5786 = [71197741156, 318187732142, 389769243308, 97679888657, 3434488093, 0, 0, 0] := by
  decide +kernel

theorem rows5787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5787 = true := by
  decide +kernel

theorem tot5787 : totK PD2M8K2 D2M8K2.t5787 = [161969214583, 447261548985, 284603082854, 30524589717, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
