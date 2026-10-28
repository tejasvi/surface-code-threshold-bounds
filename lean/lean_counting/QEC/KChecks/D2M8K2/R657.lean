import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2628 = true := by
  decide +kernel

theorem tot2628 : totK PD2M8K2 D2M8K2.t2628 = [0, 2987701732, 192014409920, 479132461885, 186865673064, 8706415949, 0, 0] := by
  decide +kernel

theorem rows2629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2629 = true := by
  decide +kernel

theorem tot2629 : totK PD2M8K2 D2M8K2.t2629 = [0, 206071964635, 470036193108, 230740531247, 22045224342, 0, 0, 0] := by
  decide +kernel

theorem rows2630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2630 = true := by
  decide +kernel

theorem tot2630 : totK PD2M8K2 D2M8K2.t2630 = [0, 186702684880, 473217389014, 222448070138, 12433893103, 0, 0, 0] := by
  decide +kernel

theorem rows2631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2631 = true := by
  decide +kernel

theorem tot2631 : totK PD2M8K2 D2M8K2.t2631 = [0, 19374756099, 330143385667, 471097948576, 82614775052, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
