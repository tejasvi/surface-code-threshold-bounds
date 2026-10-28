import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5584 = true := by
  decide +kernel

theorem tot5584 : totK PD2M8K2 D2M8K2.t5584 = [0, 271824859955, 516129468909, 104728614865, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows5585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5585 = true := by
  decide +kernel

theorem tot5585 : totK PD2M8K2 D2M8K2.t5585 = [104705589965, 349120369863, 336739008607, 94161450385, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows5586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5586 = true := by
  decide +kernel

theorem tot5586 : totK PD2M8K2 D2M8K2.t5586 = [204843362277, 456334519137, 232738724701, 25023363118, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5587 = true := by
  decide +kernel

theorem tot5587 : totK PD2M8K2 D2M8K2.t5587 = [91836339268, 414984719000, 363762255664, 31842584633, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
