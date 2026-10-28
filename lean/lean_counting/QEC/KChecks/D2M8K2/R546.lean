import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2184 = true := by
  decide +kernel

theorem tot2184 : totK PD2M8K2 D2M8K2.t2184 = [0, 0, 205231067811, 470810406029, 203104755240, 12680714061, 0, 0] := by
  decide +kernel

theorem rows2185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2185 = true := by
  decide +kernel

theorem tot2185 : totK PD2M8K2 D2M8K2.t2185 = [0, 0, 192847767439, 480994193663, 202055814956, 9840992866, 0, 0] := by
  decide +kernel

theorem rows2186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2186 = true := by
  decide +kernel

theorem tot2186 : totK PD2M8K2 D2M8K2.t2186 = [0, 0, 177710776945, 476240684692, 208517056433, 6239403452, 0, 0] := by
  decide +kernel

theorem rows2187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2187 = true := by
  decide +kernel

theorem tot2187 : totK PD2M8K2 D2M8K2.t2187 = [0, 0, 0, 297705380063, 464697969602, 84011924721, 1206465782, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
