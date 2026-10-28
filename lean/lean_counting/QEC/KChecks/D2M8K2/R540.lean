import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2160 = true := by
  decide +kernel

theorem tot2160 : totK PD2M8K2 D2M8K2.t2160 = [0, 0, 175691970083, 463817043974, 255399860466, 18796629394, 0, 0] := by
  decide +kernel

theorem rows2161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2161 = true := by
  decide +kernel

theorem tot2161 : totK PD2M8K2 D2M8K2.t2161 = [0, 0, 209497113312, 481039736393, 198769849390, 7648441037, 0, 0] := by
  decide +kernel

theorem rows2162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2162 = true := by
  decide +kernel

theorem tot2162 : totK PD2M8K2 D2M8K2.t2162 = [0, 0, 175164747206, 460586456439, 246979920888, 17400975237, 0, 0] := by
  decide +kernel

theorem rows2163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2163 = true := by
  decide +kernel

theorem tot2163 : totK PD2M8K2 D2M8K2.t2163 = [0, 0, 177226638563, 456171217204, 232723159614, 16946756371, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
