import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13444 = true := by
  decide +kernel

theorem tot13444 : totK PD2M8K2 D2M8K2.t13444 = [0, 0, 171045894958, 472901567291, 247323031918, 11583569520, 0, 0] := by
  decide +kernel

theorem rows13445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13445 = true := by
  decide +kernel

theorem tot13445 : totK PD2M8K2 D2M8K2.t13445 = [0, 0, 0, 243344604277, 510397552492, 126737317976, 2309606161, 0] := by
  decide +kernel

theorem rows13446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13446 = true := by
  decide +kernel

theorem tot13446 : totK PD2M8K2 D2M8K2.t13446 = [0, 0, 83864118156, 287826874738, 359246857614, 128837473049, 10740121073, 0] := by
  decide +kernel

theorem rows13447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13447 = true := by
  decide +kernel

theorem tot13447 : totK PD2M8K2 D2M8K2.t13447 = [0, 0, 175694344263, 464813580286, 250412035794, 19499327181, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
