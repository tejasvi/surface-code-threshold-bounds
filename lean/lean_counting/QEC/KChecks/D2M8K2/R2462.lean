import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9848 = true := by
  decide +kernel

theorem tot9848 : totK PD2M8K2 D2M8K2.t9848 = [0, 0, 192625590682, 475753386853, 219133457179, 12439805748, 0, 0] := by
  decide +kernel

theorem rows9849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9849 = true := by
  decide +kernel

theorem tot9849 : totK PD2M8K2 D2M8K2.t9849 = [0, 0, 4187820809, 313343494995, 466134705725, 89199916630, 1171084559, 0] := by
  decide +kernel

theorem rows9850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9850 = true := by
  decide +kernel

theorem tot9850 : totK PD2M8K2 D2M8K2.t9850 = [0, 0, 0, 205698014964, 447392696053, 187230465404, 11934365838, 0] := by
  decide +kernel

theorem rows9851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9851 = true := by
  decide +kernel

theorem tot9851 : totK PD2M8K2 D2M8K2.t9851 = [0, 0, 180533609873, 454983704227, 244728468686, 19635349523, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
