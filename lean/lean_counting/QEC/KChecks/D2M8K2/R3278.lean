import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13112 = true := by
  decide +kernel

theorem tot13112 : totK PD2M8K2 D2M8K2.t13112 = [0, 0, 183706201931, 462251808051, 247392868203, 23901228117, 0, 0] := by
  decide +kernel

theorem rows13113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13113 = true := by
  decide +kernel

theorem tot13113 : totK PD2M8K2 D2M8K2.t13113 = [0, 0, 177279462489, 459875287396, 242121070154, 16914626916, 0, 0] := by
  decide +kernel

theorem rows13114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13114 = true := by
  decide +kernel

theorem tot13114 : totK PD2M8K2 D2M8K2.t13114 = [0, 0, 0, 360301925781, 490857285506, 55518854629, 0, 0] := by
  decide +kernel

theorem rows13115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13115 = true := by
  decide +kernel

theorem tot13115 : totK PD2M8K2 D2M8K2.t13115 = [0, 0, 138293598013, 359865476859, 320014605374, 80804970290, 1415142070, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
