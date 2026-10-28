import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13624 = true := by
  decide +kernel

theorem tot13624 : totK PD2M8K2 D2M8K2.t13624 = [0, 0, 310324476392, 463741998850, 76948090371, 1138244013, 0, 0] := by
  decide +kernel

theorem rows13625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13625 = true := by
  decide +kernel

theorem tot13625 : totK PD2M8K2 D2M8K2.t13625 = [0, 189119387589, 478681820028, 218544305911, 11051716772, 0, 0, 0] := by
  decide +kernel

theorem rows13626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13626 = true := by
  decide +kernel

theorem tot13626 : totK PD2M8K2 D2M8K2.t13626 = [0, 190858336209, 465203265262, 219433490280, 12370590376, 0, 0, 0] := by
  decide +kernel

theorem rows13627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13627 = true := by
  decide +kernel

theorem tot13627 : totK PD2M8K2 D2M8K2.t13627 = [0, 172164365303, 471216427179, 233543445746, 13419997576, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
