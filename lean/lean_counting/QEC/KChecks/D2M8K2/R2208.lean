import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8832 = true := by
  decide +kernel

theorem tot8832 : totK PD2M8K2 D2M8K2.t8832 = [0, 0, 190552233866, 462772186733, 224075369164, 9930239593, 0, 0] := by
  decide +kernel

theorem rows8833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8833 = true := by
  decide +kernel

theorem tot8833 : totK PD2M8K2 D2M8K2.t8833 = [0, 0, 38228932023, 379514400006, 435869212052, 46103686494, 0, 0] := by
  decide +kernel

theorem rows8834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8834 = true := by
  decide +kernel

theorem tot8834 : totK PD2M8K2 D2M8K2.t8834 = [0, 0, 0, 191261524894, 496662907188, 170074778341, 3647390732, 0] := by
  decide +kernel

theorem rows8835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8835 = true := by
  decide +kernel

theorem tot8835 : totK PD2M8K2 D2M8K2.t8835 = [173526806713, 428665407054, 186617504486, 9852138406, 32599397293, 49492087454, 5886361114, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
