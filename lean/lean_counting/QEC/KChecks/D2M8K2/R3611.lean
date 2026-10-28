import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14444 = true := by
  decide +kernel

theorem tot14444 : totK PD2M8K2 D2M8K2.t14444 = [0, 189115115505, 474744188085, 218941719607, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows14445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14445 = true := by
  decide +kernel

theorem tot14445 : totK PD2M8K2 D2M8K2.t14445 = [0, 171168219543, 442984396498, 228137743967, 17714277454, 0, 0, 0] := by
  decide +kernel

theorem rows14446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14446 = true := by
  decide +kernel

theorem tot14446 : totK PD2M8K2 D2M8K2.t14446 = [0, 87479108234, 375545128456, 338996586290, 65068354131, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14447 = true := by
  decide +kernel

theorem tot14447 : totK PD2M8K2 D2M8K2.t14447 = [0, 0, 318996831990, 459024654750, 71820374511, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
