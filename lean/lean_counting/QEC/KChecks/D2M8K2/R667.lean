import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2668 = true := by
  decide +kernel

theorem tot2668 : totK PD2M8K2 D2M8K2.t2668 = [0, 36240580073, 215262606431, 441199744711, 195840755278, 8166240555, 0, 0] := by
  decide +kernel

theorem rows2669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2669 = true := by
  decide +kernel

theorem tot2669 : totK PD2M8K2 D2M8K2.t2669 = [0, 187563293171, 460325935038, 250067220339, 23167094600, 0, 0, 0] := by
  decide +kernel

theorem rows2670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2670 = true := by
  decide +kernel

theorem tot2670 : totK PD2M8K2 D2M8K2.t2670 = [0, 185778926948, 479137085714, 224653708492, 12340935526, 0, 0, 0] := by
  decide +kernel

theorem rows2671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2671 = true := by
  decide +kernel

theorem tot2671 : totK PD2M8K2 D2M8K2.t2671 = [0, 26650930622, 309885356102, 458599001909, 98161377284, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
