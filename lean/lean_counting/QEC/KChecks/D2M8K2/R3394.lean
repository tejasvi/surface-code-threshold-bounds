import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13576 = true := by
  decide +kernel

theorem tot13576 : totK PD2M8K2 D2M8K2.t13576 = [85534938331, 349928964728, 366298446590, 117278828589, 13019738321, 0, 0, 0] := by
  decide +kernel

theorem rows13577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13577 = true := by
  decide +kernel

theorem tot13577 : totK PD2M8K2 D2M8K2.t13577 = [0, 189562421577, 465244223979, 230798211701, 12032059194, 0, 0, 0] := by
  decide +kernel

theorem rows13578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13578 = true := by
  decide +kernel

theorem tot13578 : totK PD2M8K2 D2M8K2.t13578 = [152834115350, 369357808724, 275593403503, 107215009354, 6788293068, 0, 0, 0] := by
  decide +kernel

theorem rows13579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13579 = true := by
  decide +kernel

theorem tot13579 : totK PD2M8K2 D2M8K2.t13579 = [170370289897, 437805889128, 277753507307, 28509765672, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
