import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8852 = true := by
  decide +kernel

theorem tot8852 : totK PD2M8K2 D2M8K2.t8852 = [92232705550, 342656920379, 384290058564, 87928065476, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows8853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8853 = true := by
  decide +kernel

theorem tot8853 : totK PD2M8K2 D2M8K2.t8853 = [0, 213667692016, 467935236993, 180740402751, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows8854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8854 = true := by
  decide +kernel

theorem tot8854 : totK PD2M8K2 D2M8K2.t8854 = [0, 183429468002, 474964836588, 221830055657, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows8855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8855 = true := by
  decide +kernel

theorem tot8855 : totK PD2M8K2 D2M8K2.t8855 = [0, 186593726651, 446639666845, 220757665490, 16632994142, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
