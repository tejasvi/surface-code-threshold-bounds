import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5908 = true := by
  decide +kernel

theorem tot5908 : totK PD2M8K2 D2M8K2.t5908 = [0, 205932893616, 480186123672, 207800850522, 9788235105, 0, 0, 0] := by
  decide +kernel

theorem rows5909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5909 = true := by
  decide +kernel

theorem tot5909 : totK PD2M8K2 D2M8K2.t5909 = [0, 180071406952, 479318928160, 237178519884, 12203296208, 0, 0, 0] := by
  decide +kernel

theorem rows5910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5910 = true := by
  decide +kernel

theorem tot5910 : totK PD2M8K2 D2M8K2.t5910 = [0, 157164107747, 469298445669, 253979781806, 14954949818, 0, 0, 0] := by
  decide +kernel

theorem rows5911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5911 = true := by
  decide +kernel

theorem tot5911 : totK PD2M8K2 D2M8K2.t5911 = [0, 213554220365, 478362379439, 208163439757, 11066126582, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
