import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2792 = true := by
  decide +kernel

theorem tot2792 : totK PD2M8K2 D2M8K2.t2792 = [0, 0, 93211394557, 417096245858, 374014717396, 32622857229, 0, 0] := by
  decide +kernel

theorem rows2793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2793 = true := by
  decide +kernel

theorem tot2793 : totK PD2M8K2 D2M8K2.t2793 = [0, 0, 0, 235118187816, 484421255777, 135295201166, 2465685039, 0] := by
  decide +kernel

theorem rows2794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2794 = true := by
  decide +kernel

theorem tot2794 : totK PD2M8K2 D2M8K2.t2794 = [179387649462, 362512369882, 103906829395, 20959811131, 134712615267, 97752493894, 7068066807, 0] := by
  decide +kernel

theorem rows2795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2795 = true := by
  decide +kernel

theorem tot2795 : totK PD2M8K2 D2M8K2.t2795 = [156016803149, 451187972015, 253998127613, 18197172049, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
