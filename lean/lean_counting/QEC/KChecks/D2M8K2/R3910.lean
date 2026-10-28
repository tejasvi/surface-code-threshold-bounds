import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15640 = true := by
  decide +kernel

theorem tot15640 : totK PD2M8K2 D2M8K2.t15640 = [0, 100413243383, 376059658112, 391757255753, 52829737455, 0, 0, 0] := by
  decide +kernel

theorem rows15641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15641 = true := by
  decide +kernel

theorem tot15641 : totK PD2M8K2 D2M8K2.t15641 = [0, 194839249256, 470782327293, 235294247044, 15260493862, 0, 0, 0] := by
  decide +kernel

theorem rows15642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15642 = true := by
  decide +kernel

theorem tot15642 : totK PD2M8K2 D2M8K2.t15642 = [0, 121150445789, 441446739715, 319781116011, 36700346791, 0, 0, 0] := by
  decide +kernel

theorem rows15643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15643 = true := by
  decide +kernel

theorem tot15643 : totK PD2M8K2 D2M8K2.t15643 = [0, 0, 176091859297, 445331812914, 257730790267, 25114608015, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
