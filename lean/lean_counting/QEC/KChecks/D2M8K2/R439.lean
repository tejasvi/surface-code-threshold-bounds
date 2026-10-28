import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1756 = true := by
  decide +kernel

theorem tot1756 : totK PD2M8K2 D2M8K2.t1756 = [0, 0, 171546251453, 447409268304, 256785432195, 17058800342, 0, 0] := by
  decide +kernel

theorem rows1757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1757 = true := by
  decide +kernel

theorem tot1757 : totK PD2M8K2 D2M8K2.t1757 = [0, 0, 162005319714, 465834934503, 262433195403, 15130787922, 0, 0] := by
  decide +kernel

theorem rows1758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1758 = true := by
  decide +kernel

theorem tot1758 : totK PD2M8K2 D2M8K2.t1758 = [0, 0, 0, 298777141809, 491649777477, 88059666768, 1096505104, 0] := by
  decide +kernel

theorem rows1759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1759 = true := by
  decide +kernel

theorem tot1759 : totK PD2M8K2 D2M8K2.t1759 = [0, 0, 118657156765, 356144037981, 321317158262, 86201493137, 3884009855, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
