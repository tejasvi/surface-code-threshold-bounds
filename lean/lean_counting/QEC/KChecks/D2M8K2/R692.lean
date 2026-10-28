import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2768 = true := by
  decide +kernel

theorem tot2768 : totK PD2M8K2 D2M8K2.t2768 = [0, 159474955900, 445862531049, 274267937079, 24977183528, 0, 0, 0] := by
  decide +kernel

theorem rows2769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2769 = true := by
  decide +kernel

theorem tot2769 : totK PD2M8K2 D2M8K2.t2769 = [0, 89359567243, 354830928551, 373360345789, 76105064245, 1129969115, 0, 0] := by
  decide +kernel

theorem rows2770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2770 = true := by
  decide +kernel

theorem tot2770 : totK PD2M8K2 D2M8K2.t2770 = [0, 0, 226602537759, 496466596349, 160005553922, 6749059647, 0, 0] := by
  decide +kernel

theorem rows2771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2771 = true := by
  decide +kernel

theorem tot2771 : totK PD2M8K2 D2M8K2.t2771 = [0, 165497800747, 429825346183, 262164875788, 46355283728, 1189515370, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
