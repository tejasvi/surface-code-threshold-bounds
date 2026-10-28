import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4892 = true := by
  decide +kernel

theorem tot4892 : totK PD2M8K2 D2M8K2.t4892 = [0, 0, 193201329576, 475984573532, 224644528419, 15323388730, 0, 0] := by
  decide +kernel

theorem rows4893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4893 = true := by
  decide +kernel

theorem tot4893 : totK PD2M8K2 D2M8K2.t4893 = [0, 0, 104481721833, 420452132081, 351409864612, 47310182296, 0, 0] := by
  decide +kernel

theorem rows4894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4894 = true := by
  decide +kernel

theorem tot4894 : totK PD2M8K2 D2M8K2.t4894 = [0, 0, 0, 207342563439, 471367886745, 216403060726, 13656771860, 0] := by
  decide +kernel

theorem rows4895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4895 = true := by
  decide +kernel

theorem tot4895 : totK PD2M8K2 D2M8K2.t4895 = [0, 0, 107297381188, 342155292785, 351105281575, 95276549121, 1409560813, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
