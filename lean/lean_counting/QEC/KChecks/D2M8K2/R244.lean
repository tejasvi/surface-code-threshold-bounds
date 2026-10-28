import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t976 = true := by
  decide +kernel

theorem tot976 : totK PD2M8K2 D2M8K2.t976 = [0, 197601811551, 477251431056, 203770843273, 9951931981, 0, 0, 0] := by
  decide +kernel

theorem rows977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t977 = true := by
  decide +kernel

theorem tot977 : totK PD2M8K2 D2M8K2.t977 = [0, 195148410243, 461615575677, 219036873042, 16912215996, 0, 0, 0] := by
  decide +kernel

theorem rows978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t978 = true := by
  decide +kernel

theorem tot978 : totK PD2M8K2 D2M8K2.t978 = [0, 212617849456, 487490474258, 169253834191, 4978993093, 0, 0, 0] := by
  decide +kernel

theorem rows979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t979 = true := by
  decide +kernel

theorem tot979 : totK PD2M8K2 D2M8K2.t979 = [0, 0, 302686475324, 467215047335, 83888814731, 1206465782, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
