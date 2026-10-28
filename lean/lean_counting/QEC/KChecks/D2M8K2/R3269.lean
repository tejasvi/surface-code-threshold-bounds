import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13076 = true := by
  decide +kernel

theorem tot13076 : totK PD2M8K2 D2M8K2.t13076 = [0, 0, 192308754986, 472918387577, 222117699461, 12679943201, 0, 0] := by
  decide +kernel

theorem rows13077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13077 = true := by
  decide +kernel

theorem tot13077 : totK PD2M8K2 D2M8K2.t13077 = [0, 0, 171720673315, 455485229621, 231976892572, 13964593734, 0, 0] := by
  decide +kernel

theorem rows13078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13078 = true := by
  decide +kernel

theorem tot13078 : totK PD2M8K2 D2M8K2.t13078 = [0, 0, 181642324046, 475268813598, 212151654073, 9757737807, 0, 0] := by
  decide +kernel

theorem rows13079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13079 = true := by
  decide +kernel

theorem tot13079 : totK PD2M8K2 D2M8K2.t13079 = [0, 0, 195944577466, 465827943718, 209479224504, 12403393969, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
