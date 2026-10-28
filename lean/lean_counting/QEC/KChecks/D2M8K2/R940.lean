import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3760 = true := by
  decide +kernel

theorem tot3760 : totK PD2M8K2 D2M8K2.t3760 = [0, 274214598282, 494370190195, 112464528507, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows3761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3761 = true := by
  decide +kernel

theorem tot3761 : totK PD2M8K2 D2M8K2.t3761 = [100428189712, 376802510286, 396647484119, 51108165586, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3762 = true := by
  decide +kernel

theorem tot3762 : totK PD2M8K2 D2M8K2.t3762 = [199839133489, 481408722485, 228353944829, 14557144966, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3763 = true := by
  decide +kernel

theorem tot3763 : totK PD2M8K2 D2M8K2.t3763 = [117135509096, 429066520911, 329428311199, 36934985574, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
