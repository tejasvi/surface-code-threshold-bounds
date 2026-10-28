import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13888 = true := by
  decide +kernel

theorem tot13888 : totK PD2M8K2 D2M8K2.t13888 = [180705534571, 463958435147, 238910214615, 16711677162, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13889 = true := by
  decide +kernel

theorem tot13889 : totK PD2M8K2 D2M8K2.t13889 = [89337167127, 400152915915, 362343505155, 67803330877, 5319205844, 0, 0, 0] := by
  decide +kernel

theorem rows13890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13890 = true := by
  decide +kernel

theorem tot13890 : totK PD2M8K2 D2M8K2.t13890 = [0, 173180571335, 453274845752, 247402091861, 18352726590, 0, 0, 0] := by
  decide +kernel

theorem rows13891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13891 = true := by
  decide +kernel

theorem tot13891 : totK PD2M8K2 D2M8K2.t13891 = [3757117624, 161549973495, 463514465074, 257612979093, 12231701805, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
