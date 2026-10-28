import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12880 = true := by
  decide +kernel

theorem tot12880 : totK PD2M8K2 D2M8K2.t12880 = [0, 0, 155928167669, 467256656866, 262132847406, 16385090698, 0, 0] := by
  decide +kernel

theorem rows12881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12881 = true := by
  decide +kernel

theorem tot12881 : totK PD2M8K2 D2M8K2.t12881 = [0, 0, 0, 318956232187, 464679074976, 94088842684, 1444560764, 0] := by
  decide +kernel

theorem rows12882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12882 = true := by
  decide +kernel

theorem tot12882 : totK PD2M8K2 D2M8K2.t12882 = [0, 0, 161638900319, 451173308249, 276932441626, 31420422000, 0, 0] := by
  decide +kernel

theorem rows12883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12883 = true := by
  decide +kernel

theorem tot12883 : totK PD2M8K2 D2M8K2.t12883 = [0, 0, 172783723090, 453658695587, 256203224748, 17157043897, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
