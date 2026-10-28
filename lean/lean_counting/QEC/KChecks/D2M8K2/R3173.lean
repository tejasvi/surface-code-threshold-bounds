import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12692 = true := by
  decide +kernel

theorem tot12692 : totK PD2M8K2 D2M8K2.t12692 = [0, 0, 0, 358859540395, 485258307103, 67251094705, 0, 0] := by
  decide +kernel

theorem rows12693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12693 = true := by
  decide +kernel

theorem tot12693 : totK PD2M8K2 D2M8K2.t12693 = [0, 0, 163675580057, 386965399476, 277217771611, 69278453915, 1409560813, 0] := by
  decide +kernel

theorem rows12694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12694 = true := by
  decide +kernel

theorem tot12694 : totK PD2M8K2 D2M8K2.t12694 = [0, 0, 178354053085, 466848923490, 239032669648, 12149614790, 0, 0] := by
  decide +kernel

theorem rows12695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12695 = true := by
  decide +kernel

theorem tot12695 : totK PD2M8K2 D2M8K2.t12695 = [0, 0, 65563964900, 319960117839, 408544102186, 73950180366, 1164319620, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
