import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3840 = true := by
  decide +kernel

theorem tot3840 : totK PD2M8K2 D2M8K2.t3840 = [171375571942, 444366502402, 265273365444, 36686749307, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3841 = true := by
  decide +kernel

theorem tot3841 : totK PD2M8K2 D2M8K2.t3841 = [158134426311, 450234878667, 267308047265, 18308308992, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3842 = true := by
  decide +kernel

theorem tot3842 : totK PD2M8K2 D2M8K2.t3842 = [89913192444, 341729506771, 380688400315, 83143889942, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows3843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3843 = true := by
  decide +kernel

theorem tot3843 : totK PD2M8K2 D2M8K2.t3843 = [0, 224969854063, 475250422919, 169073521641, 9465717894, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
