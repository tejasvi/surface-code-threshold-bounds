import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t660 = true := by
  decide +kernel

theorem tot660 : totK PD2M8K2 D2M8K2.t660 = [120695740156, 351160717341, 310771612896, 112885925698, 6672620744, 0, 0, 0] := by
  decide +kernel

theorem rows661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t661 = true := by
  decide +kernel

theorem tot661 : totK PD2M8K2 D2M8K2.t661 = [170244865317, 448882099931, 278334567420, 29793303894, 0, 0, 0, 0] := by
  decide +kernel

theorem rows662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t662 = true := by
  decide +kernel

theorem tot662 : totK PD2M8K2 D2M8K2.t662 = [151565813020, 454322289825, 283733424720, 19811840447, 0, 0, 0, 0] := by
  decide +kernel

theorem rows663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t663 = true := by
  decide +kernel

theorem tot663 : totK PD2M8K2 D2M8K2.t663 = [0, 231484268260, 502753815132, 161989408504, 5768874209, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
