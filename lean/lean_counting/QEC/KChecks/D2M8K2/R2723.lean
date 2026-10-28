import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10892 = true := by
  decide +kernel

theorem tot10892 : totK PD2M8K2 D2M8K2.t10892 = [0, 0, 192774152041, 471605667541, 225049392321, 12900833004, 0, 0] := by
  decide +kernel

theorem rows10893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10893 = true := by
  decide +kernel

theorem tot10893 : totK PD2M8K2 D2M8K2.t10893 = [0, 0, 176269535765, 442785198916, 272237996076, 27190566548, 0, 0] := by
  decide +kernel

theorem rows10894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10894 = true := by
  decide +kernel

theorem tot10894 : totK PD2M8K2 D2M8K2.t10894 = [0, 0, 136668606607, 450708032507, 287658366408, 18611991986, 0, 0] := by
  decide +kernel

theorem rows10895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10895 = true := by
  decide +kernel

theorem tot10895 : totK PD2M8K2 D2M8K2.t10895 = [0, 0, 0, 210973635442, 476291831927, 176555745747, 9633262574, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
