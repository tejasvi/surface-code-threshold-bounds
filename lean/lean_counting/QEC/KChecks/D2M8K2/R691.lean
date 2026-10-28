import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2764 = true := by
  decide +kernel

theorem tot2764 : totK PD2M8K2 D2M8K2.t2764 = [0, 162975290697, 472023700392, 268866753333, 18026531296, 0, 0, 0] := by
  decide +kernel

theorem rows2765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2765 = true := by
  decide +kernel

theorem tot2765 : totK PD2M8K2 D2M8K2.t2765 = [0, 0, 170418774302, 443743147956, 256546460228, 25316940874, 0, 0] := by
  decide +kernel

theorem rows2766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2766 = true := by
  decide +kernel

theorem tot2766 : totK PD2M8K2 D2M8K2.t2766 = [0, 0, 220175406294, 493072351471, 187589963356, 5358820111, 0, 0] := by
  decide +kernel

theorem rows2767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2767 = true := by
  decide +kernel

theorem tot2767 : totK PD2M8K2 D2M8K2.t2767 = [0, 165400824333, 375393809244, 251050824638, 104033855356, 6804944647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
