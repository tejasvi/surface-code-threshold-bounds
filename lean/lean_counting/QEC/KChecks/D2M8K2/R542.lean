import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2168 = true := by
  decide +kernel

theorem tot2168 : totK PD2M8K2 D2M8K2.t2168 = [0, 0, 292192330820, 509314738144, 97491984530, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2169 = true := by
  decide +kernel

theorem tot2169 : totK PD2M8K2 D2M8K2.t2169 = [0, 179491426632, 433952544255, 272223335982, 33122120570, 0, 0, 0] := by
  decide +kernel

theorem rows2170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2170 = true := by
  decide +kernel

theorem tot2170 : totK PD2M8K2 D2M8K2.t2170 = [0, 173200233819, 454480996977, 247342341106, 18339826511, 0, 0, 0] := by
  decide +kernel

theorem rows2171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2171 = true := by
  decide +kernel

theorem tot2171 : totK PD2M8K2 D2M8K2.t2171 = [0, 29655820042, 267163679550, 406254514630, 186715661505, 19839770084, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
