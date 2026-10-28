import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2868 = true := by
  decide +kernel

theorem tot2868 : totK PD2M8K2 D2M8K2.t2868 = [14620948355, 180022676844, 463214702995, 225479904731, 9331067253, 0, 0, 0] := by
  decide +kernel

theorem rows2869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2869 = true := by
  decide +kernel

theorem tot2869 : totK PD2M8K2 D2M8K2.t2869 = [179053738513, 469754504383, 248630227600, 23124774842, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2870 = true := by
  decide +kernel

theorem tot2870 : totK PD2M8K2 D2M8K2.t2870 = [195475297929, 481134905066, 225755993829, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2871 = true := by
  decide +kernel

theorem tot2871 : totK PD2M8K2 D2M8K2.t2871 = [52518175507, 326842685439, 429908300682, 91395619631, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
