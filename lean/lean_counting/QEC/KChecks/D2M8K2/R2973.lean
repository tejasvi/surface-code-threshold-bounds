import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11892 = true := by
  decide +kernel

theorem tot11892 : totK PD2M8K2 D2M8K2.t11892 = [0, 158454064037, 478088547419, 244880840320, 10903241412, 0, 0, 0] := by
  decide +kernel

theorem rows11893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11893 = true := by
  decide +kernel

theorem tot11893 : totK PD2M8K2 D2M8K2.t11893 = [0, 203976899211, 477288711476, 197404300029, 7870241454, 0, 0, 0] := by
  decide +kernel

theorem rows11894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11894 = true := by
  decide +kernel

theorem tot11894 : totK PD2M8K2 D2M8K2.t11894 = [142990683665, 329655084271, 304376927593, 140815989297, 13468148062, 0, 0, 0] := by
  decide +kernel

theorem rows11895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11895 = true := by
  decide +kernel

theorem tot11895 : totK PD2M8K2 D2M8K2.t11895 = [193194056100, 468048623596, 232114865806, 15474652264, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
