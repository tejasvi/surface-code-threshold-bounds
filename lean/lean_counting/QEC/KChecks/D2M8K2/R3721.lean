import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14884 = true := by
  decide +kernel

theorem tot14884 : totK PD2M8K2 D2M8K2.t14884 = [0, 238227132044, 492502283002, 158659469989, 8407441191, 0, 0, 0] := by
  decide +kernel

theorem rows14885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14885 = true := by
  decide +kernel

theorem tot14885 : totK PD2M8K2 D2M8K2.t14885 = [126426574475, 369176695211, 315729267694, 78817750494, 3331292818, 0, 0, 0] := by
  decide +kernel

theorem rows14886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14886 = true := by
  decide +kernel

theorem tot14886 : totK PD2M8K2 D2M8K2.t14886 = [169772273150, 438166511761, 274417362848, 30271926621, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14887 = true := by
  decide +kernel

theorem tot14887 : totK PD2M8K2 D2M8K2.t14887 = [122667495314, 435253695843, 318416598451, 27541820536, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
