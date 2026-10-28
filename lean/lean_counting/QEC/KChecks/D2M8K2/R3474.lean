import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13896 = true := by
  decide +kernel

theorem tot13896 : totK PD2M8K2 D2M8K2.t13896 = [196700539931, 460998580012, 242458813511, 23250197218, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13897 = true := by
  decide +kernel

theorem tot13897 : totK PD2M8K2 D2M8K2.t13897 = [183317949398, 475006010923, 226707763010, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13898 = true := by
  decide +kernel

theorem tot13898 : totK PD2M8K2 D2M8K2.t13898 = [4159550692, 300910971893, 480873368670, 110727846974, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows13899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13899 = true := by
  decide +kernel

theorem tot13899 : totK PD2M8K2 D2M8K2.t13899 = [7518713851, 194104741341, 462956330808, 195195909701, 12052611869, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
