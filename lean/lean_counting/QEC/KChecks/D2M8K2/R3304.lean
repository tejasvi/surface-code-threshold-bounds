import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13216 = true := by
  decide +kernel

theorem tot13216 : totK PD2M8K2 D2M8K2.t13216 = [0, 179004309973, 373861826520, 224697167786, 124388160521, 13646095762, 0, 0] := by
  decide +kernel

theorem rows13217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13217 = true := by
  decide +kernel

theorem tot13217 : totK PD2M8K2 D2M8K2.t13217 = [0, 174185781161, 460663941088, 244390352315, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows13218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13218 = true := by
  decide +kernel

theorem tot13218 : totK PD2M8K2 D2M8K2.t13218 = [0, 82104467767, 367869526341, 363108527023, 68267335197, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13219 = true := by
  decide +kernel

theorem tot13219 : totK PD2M8K2 D2M8K2.t13219 = [0, 0, 307564660943, 519892724481, 78098710999, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
