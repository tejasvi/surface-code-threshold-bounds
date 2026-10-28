import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4852 = true := by
  decide +kernel

theorem tot4852 : totK PD2M8K2 D2M8K2.t4852 = [0, 0, 92353366773, 392383981302, 368266637035, 47068679047, 0, 0] := by
  decide +kernel

theorem rows4853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4853 = true := by
  decide +kernel

theorem tot4853 : totK PD2M8K2 D2M8K2.t4853 = [0, 0, 0, 256714006205, 508441148835, 135559166891, 1284661075, 0] := by
  decide +kernel

theorem rows4854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4854 = true := by
  decide +kernel

theorem tot4854 : totK PD2M8K2 D2M8K2.t4854 = [0, 0, 88614338806, 250823505338, 343975955955, 183780261719, 12366239339, 0] := by
  decide +kernel

theorem rows4855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4855 = true := by
  decide +kernel

theorem tot4855 : totK PD2M8K2 D2M8K2.t4855 = [0, 0, 220911097532, 488445773375, 178033578172, 8633570784, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
