import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1584 = true := by
  decide +kernel

theorem tot1584 : totK PD2M8K2 D2M8K2.t1584 = [0, 180936684967, 442595716413, 251777561710, 21502934562, 0, 0, 0] := by
  decide +kernel

theorem rows1585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1585 = true := by
  decide +kernel

theorem tot1585 : totK PD2M8K2 D2M8K2.t1585 = [0, 61647779834, 348434873889, 389332686660, 76838365689, 1096505104, 0, 0] := by
  decide +kernel

theorem rows1586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1586 = true := by
  decide +kernel

theorem tot1586 : totK PD2M8K2 D2M8K2.t1586 = [0, 14495993721, 260473583024, 493993645166, 123294151533, 3884009855, 0, 0] := by
  decide +kernel

theorem rows1587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1587 = true := by
  decide +kernel

theorem tot1587 : totK PD2M8K2 D2M8K2.t1587 = [0, 181999663962, 460013498997, 234941831925, 21179855894, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
