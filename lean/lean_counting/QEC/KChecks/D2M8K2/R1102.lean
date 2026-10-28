import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4408 = true := by
  decide +kernel

theorem tot4408 : totK PD2M8K2 D2M8K2.t4408 = [0, 157218327240, 376349015806, 281225278871, 88611809461, 3880716147, 0, 0] := by
  decide +kernel

theorem rows4409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4409 = true := by
  decide +kernel

theorem tot4409 : totK PD2M8K2 D2M8K2.t4409 = [0, 167906153408, 458825771149, 268568457721, 20351827574, 0, 0, 0] := by
  decide +kernel

theorem rows4410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4410 = true := by
  decide +kernel

theorem tot4410 : totK PD2M8K2 D2M8K2.t4410 = [0, 92350536064, 349558679974, 375678149848, 86585521210, 1267860612, 0, 0] := by
  decide +kernel

theorem rows4411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4411 = true := by
  decide +kernel

theorem tot4411 : totK PD2M8K2 D2M8K2.t4411 = [0, 0, 219198303445, 493132351752, 175026195518, 6127206079, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
