import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2004 = true := by
  decide +kernel

theorem tot2004 : totK PD2M8K2 D2M8K2.t2004 = [0, 41520926685, 315771019076, 429516738780, 97385303145, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2005 = true := by
  decide +kernel

theorem tot2005 : totK PD2M8K2 D2M8K2.t2005 = [0, 65749877802, 354169416198, 441954663745, 55667898030, 0, 0, 0] := by
  decide +kernel

theorem rows2006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2006 = true := by
  decide +kernel

theorem tot2006 : totK PD2M8K2 D2M8K2.t2006 = [0, 165152532560, 455044409741, 270973311074, 25424911896, 0, 0, 0] := by
  decide +kernel

theorem rows2007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2007 = true := by
  decide +kernel

theorem tot2007 : totK PD2M8K2 D2M8K2.t2007 = [0, 171922687869, 458768782780, 240941861993, 14531610476, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
