import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3600 = true := by
  decide +kernel

theorem tot3600 : totK PD2M8K2 D2M8K2.t3600 = [0, 182345479206, 451382882649, 264774642864, 36354034632, 1726220677, 0, 0] := by
  decide +kernel

theorem rows3601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3601 = true := by
  decide +kernel

theorem tot3601 : totK PD2M8K2 D2M8K2.t3601 = [0, 187324538729, 473669856024, 239185031693, 12549310131, 0, 0, 0] := by
  decide +kernel

theorem rows3602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3602 = true := by
  decide +kernel

theorem tot3602 : totK PD2M8K2 D2M8K2.t3602 = [0, 74713786392, 307968939394, 368607652464, 157562016274, 17186218589, 0, 0] := by
  decide +kernel

theorem rows3603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3603 = true := by
  decide +kernel

theorem tot3603 : totK PD2M8K2 D2M8K2.t3603 = [0, 0, 204555619248, 469781303741, 211797080679, 12208674056, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
