import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13804 = true := by
  decide +kernel

theorem tot13804 : totK PD2M8K2 D2M8K2.t13804 = [0, 23362993338, 373268597901, 454770338000, 56224947288, 0, 0, 0] := by
  decide +kernel

theorem rows13805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13805 = true := by
  decide +kernel

theorem tot13805 : totK PD2M8K2 D2M8K2.t13805 = [0, 47799152175, 224333215823, 442288961410, 152587534157, 5159868635, 0, 0] := by
  decide +kernel

theorem rows13806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13806 = true := by
  decide +kernel

theorem tot13806 : totK PD2M8K2 D2M8K2.t13806 = [0, 195622508046, 463639471427, 239194121665, 23121511808, 0, 0, 0] := by
  decide +kernel

theorem rows13807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13807 = true := by
  decide +kernel

theorem tot13807 : totK PD2M8K2 D2M8K2.t13807 = [0, 170874428049, 473868617470, 229777391378, 12244847212, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
